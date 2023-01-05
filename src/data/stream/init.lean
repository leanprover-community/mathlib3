/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.stream.defs
import tactic.ext
import tactic.simps
import logic.function.iterate
import data.list.basic

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.
-/

open nat function option

universes u v w
variables {α : Type u} {β : Type v} {δ : Type w} {a a₁ a₂ : α} {s s₁ s₂ : stream α} {n : ℕ}

namespace stream

initialize_simps_projections stream (nth → nth as_prefix)

attribute [simps] tail drop tails inits nats map enum zip
attribute [simps {attrs := []}] cycle

@[ext] theorem ext (h : ∀ n, nth s₁ n = nth s₂ n) : s₁ = s₂ :=
by { cases s₁, cases s₂, congr, exact funext h }

theorem ext_iff : s₁ = s₂ ↔ ∀ n, nth s₁ n = nth s₂ n := ⟨λ h n, h ▸ rfl, stream.ext⟩

instance [inhabited α] : inhabited (stream α) := ⟨pure default⟩

@[simp] theorem cons_head_tail (s : stream α) : head s :: tail s = s := by ext (_|k); refl
@[simp] theorem mk_nth (s : stream α) : mk s.nth = s := by { cases s, refl }
@[simp] theorem nth_zero (s : stream α) : nth s 0 = head s := rfl
@[simp] theorem head_cons (a : α) (s : stream α) : head (a :: s) = a := rfl
@[simp] theorem tail_cons (a : α) (s : stream α) : tail (a :: s) = s := by { cases s, refl }
@[simp] theorem drop_one (s : stream α) : drop 1 s = tail s := rfl
@[simp] theorem nth_cons_succ (n : ℕ) (s : stream α) (x : α) : nth (x :: s) (n + 1) = nth s n := rfl
@[simp] theorem nth_pure (n : ℕ) (a : α) : nth (pure a) n = a := rfl

theorem ext_head_tail (h₁ : head s₁ = head s₂) (h₂ : tail s₁ = tail s₂) : s₁ = s₂ :=
by rw [← cons_head_tail s₁, h₁, h₂, cons_head_tail]

theorem tail_drop (n : ℕ) (s : stream α) : tail (drop n s) = drop n (tail s) :=
by { ext i, simp only [nth_tail, nth_drop, nat.add_right_comm] }

theorem drop_drop (n m : ℕ) (s : stream α) : drop n (drop m s) = drop (n+m) s :=
by { ext i, simp only [nth_drop, nat.add_assoc] }

theorem drop_succ (n : ℕ) (s : stream α) : drop (n + 1) s = drop n (tail s) := rfl

@[simp] lemma head_drop (s : stream α) (n : ℕ) : (s.drop n).head = s.nth n :=
congr_arg s.nth n.zero_add

@[simp] lemma drop_zero (s : stream α) : s.drop 0 = s := ext $ λ _, rfl

lemma cons_injective2 : injective2 (cons : α → stream α → stream α) :=
λ x y s t h, ⟨congr_arg head h, by rw [← tail_cons x s, h, tail_cons]⟩

lemma cons_injective_left (s : stream α) : injective (λ x, cons x s) := cons_injective2.left s

lemma cons_injective_right (x : α) : injective (cons x) := cons_injective2.right _

@[simp] lemma cons_inj : a₁::s₁ = a₂::s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ := cons_injective2.eq_iff

theorem all_def (p : α → Prop) (s : stream α) : all p s = ∀ n, p (nth s n) := rfl

theorem any_def (p : α → Prop) (s : stream α) : any p s = ∃ n, p (nth s n) := rfl

lemma mem_def : a ∈ s ↔ ∃ n, a = nth s n := iff.rfl

theorem mem_cons_iff : a₁ ∈ a₂::s ↔ a₁ = a₂ ∨ a₁ ∈ s :=
⟨by { rintro ⟨_|n,rfl⟩, exacts [or.inl rfl, or.inr ⟨n, rfl⟩] },
  by { rintro (rfl|⟨n, rfl⟩), exacts [⟨0, rfl⟩, ⟨n + 1, rfl⟩] }⟩

theorem mem_cons (a : α) (s : stream α) : a ∈ (a::s) := ⟨0, rfl⟩

theorem mem_cons_of_mem (b : α) : a ∈ s → a ∈ b :: s := mem_cons_iff.2 ∘ or.inr

theorem mem_of_nth_eq : a = nth s n → a ∈ s := exists.intro n

section map
variable (f : α → β)

theorem drop_map (n : ℕ) (s : stream α) : drop n (map f s) = map f (drop n s) := rfl

theorem tail_map (s : stream α) : tail (map f s) = map f (tail s) := rfl

@[simp] theorem head_map (s : stream α) : head (map f s) = f (head s) := rfl

@[simp] theorem map_id (s : stream α) : map id s = s := by { cases s, refl }

theorem map_eq (s : stream α) : map f s = f (head s) :: map f (tail s) :=
ext_head_tail rfl rfl

theorem map_cons (a : α) (s : stream α) : map f (a :: s) = f a :: map f s :=
ext_head_tail rfl rfl

theorem map_map (g : β → δ) (f : α → β) (s : stream α) : map g (map f s) = map (g ∘ f) s := rfl

theorem map_tail (s : stream α) : map f (tail s) = tail (map f s) := rfl

@[simp] theorem mem_map {f : α → β} {b : β} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
⟨λ ⟨n, hn⟩, ⟨_, ⟨n, rfl⟩, hn.symm⟩, λ ⟨a, ⟨n, hn⟩, ha⟩, ⟨n, ha ▸ congr_arg f hn⟩⟩

theorem mem_map_of_mem (h : a ∈ s) : f a ∈ map f s := mem_map.2 ⟨a, h, rfl⟩

end map

section zip
variable (f : α → β → δ)

theorem drop_zip (n : ℕ) (s₁ : stream α) (s₂ : stream β) :
  drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
rfl

theorem head_zip (s₁ : stream α) (s₂ : stream β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) := rfl

theorem tail_zip (s₁ : stream α) (s₂ : stream β) :
  tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) := rfl

theorem zip_eq (s₁ : stream α) (s₂ : stream β) :
  zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) :=
ext_head_tail rfl rfl

lemma enum_eq_zip (s : stream α) : enum s = zip prod.mk nats s := rfl

end zip

@[simp] theorem mem_pure {a b : α} : a ∈ (pure b : stream α) ↔ a = b :=
@exists_const (a = b) ℕ _

@[simp] theorem cons_self_pure (a : α) : (a :: pure a : stream α) = pure a :=
cons_head_tail (pure a)

@[simp] theorem tail_pure (a : α) : tail (pure a) = pure a := rfl

@[simp] theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) := rfl

@[simp] theorem drop_pure (n : ℕ) (a : α) : drop n (pure a) = pure a := rfl

@[simp] theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a := rfl

@[simp] theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := rfl

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a :: iterate f (f a) :=
ext_head_tail rfl rfl

@[simp] theorem nth_iterate (f : α → α) (a : α) (n : ℕ) : (iterate f a).nth n = (f^[n] a) := rfl

theorem nth_iterate_succ' (n : ℕ) (f : α → α) (a : α) :
  nth (iterate f a) (n + 1) = f (nth (iterate f a) n) :=
iterate_succ_apply' _ _ _

theorem nth_iterate_succ (n : ℕ) (f : α → α) (a : α) :
  nth (iterate f a) (n + 1) = nth (iterate f (f a)) n :=
rfl

theorem iterate_fixed {f : α → α} (h : f a = a) : iterate f a = pure a :=
ext $ λ n, by rw [nth_iterate, iterate_fixed h, nth_pure]

@[simp] theorem iterate_id (a : α) : iterate id a = pure a := iterate_fixed rfl

@[simp] theorem map_self_iterate (f : α → α) (a : α) : map f (iterate f a) = iterate f (f a) :=
by { ext n, simp only [nth_map, nth_iterate, (commute.iterate_self _ _).eq] }

@[simp] theorem iterate_tail' : ∀ (s : stream α) n, (tail^[n] s) = drop n s
| s 0 := by rw [iterate_zero_apply, drop_zero]
| s (n + 1) := by rw [iterate_succ_apply, drop_succ, iterate_tail']

@[simp] theorem iterate_tail (s : stream α) : iterate tail s = tails s := ext s.iterate_tail'

section corec
theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) := rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) :=
ext_head_tail rfl rfl

theorem corec_fixed (f : α → β) {g : α → α} (h : g a = a) : corec f g a = pure (f a) :=
by rw [corec, iterate_fixed h, map_pure]

@[simp] theorem corec_id (f : α → α) (a : α) : corec id f a = iterate f a := rfl

theorem corec_id_id (a : α) : corec id id a = pure a := iterate_id _

@[simp] theorem corec_head_tail (s : stream α) : corec head tail s = s :=
ext $ λ n, by rw [corec_def, nth_map, iterate_tail, nth_tails, head_drop]

end corec

section corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
corec_eq _ _ _

end corec'
section bisim
variable (R : stream α → stream α → Prop)
local infix ` ~ `:50 := R

/-- We say that a relation `~` on streams is a *bisimulation* if `s₁ ~ s₂` implies
`head s₁ = head s₂` and `tail s₁ ~ tail s₂`.  -/
def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

theorem nth_of_bisim (bisim : is_bisimulation R) :
  ∀ {s₁ s₂} n, s₁ ~ s₂ → nth s₁ n = nth s₂ n ∧ drop (n+1) s₁ ~ drop (n+1) s₂
| s₁ s₂ 0     h := bisim h
| s₁ s₂ (n+1) h := let ⟨h₁, trel⟩ := bisim h in nth_of_bisim n trel

/-- If two streams are bisimilar, then they are equal. -/
theorem eq_of_bisim (bisim : is_bisimulation R) {s₁ s₂} (h : s₁ ~ s₂) : s₁ = s₂ :=
ext $ λ n, (nth_of_bisim R bisim n h).left

end bisim

@[simp] theorem tail_eq_self : tail s = s ↔ s = pure (head s) :=
⟨λ h, ext $ λ n, by rw [nth_pure, ← head_drop, ← iterate_tail', function.iterate_fixed h],
  λ h, h.symm ▸ rfl⟩

theorem bisim_simple (s₁ s₂ : stream α) (hh : head s₁ = head s₂) (ht₁ : s₁ = tail s₁)
  (ht₂ : s₂ = tail s₂) : s₁ = s₂ :=
by rw [tail_eq_self.1 ht₁.symm, tail_eq_self.1 ht₂.symm, hh]

theorem coinduction (hh : head s₁ = head s₂)
  (ht : ∀ (β : Type u) (fr : stream α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) :
  s₁ = s₂ :=
eq_of_bisim
  (λ s₁ s₂, head s₁ = head s₂ ∧ ∀ (β : Type u) (fr : stream α → β), fr s₁ = fr s₂ →
    fr (tail s₁) = fr (tail s₂))
  (λ s₁ s₂ ⟨h₁, h₂⟩, ⟨h₁, h₂ _ head h₁, λ β f hf, h₂ β (f ∘ tail) hf⟩)
  ⟨hh, ht⟩

@[simp] theorem nth_even (s : stream α) (n : ℕ) : nth (even s) n = nth s (2 * n) :=
congr_arg s.nth $ bit0_val _

@[simp] theorem nth_odd (s : stream α) (n : ℕ) : nth (odd s) n = nth s (2 * n + 1) :=
congr_arg s.nth $ bit1_val _

@[simp] theorem head_interleave (s₁ s₂ : stream α) : head (s₁ ⋈ s₂) = head s₁ := rfl

@[simp] theorem nth_interleave_bit (n : ℕ) (s₁ s₂ : stream α) (b : bool) :
  nth (s₁ ⋈ s₂) (bit b n) = cond b (nth s₂ n) (nth s₁ n) :=
begin
  simp only [interleave, nat.bit_cases_on, eq.mpr],
  rw [nat.bodd_bit, nat.div2_bit]
end

@[simp] theorem nth_interleave_left (n : ℕ) (s₁ s₂ : stream α) : nth (s₁ ⋈ s₂) (2 * n) = nth s₁ n :=
bit0_val n ▸ nth_interleave_bit n s₁ s₂ ff

@[simp] theorem even_interleave (s₁ s₂ : stream α) : even (s₁ ⋈ s₂) = s₁ :=
ext $ λ n, nth_interleave_bit n s₁ s₂ ff

@[simp] theorem nth_interleave_right (n : ℕ) (s₁ s₂ : stream α) :
  nth (s₁ ⋈ s₂) (2 * n + 1) = nth s₂ n :=
bit1_val n ▸ nth_interleave_bit n s₁ s₂ tt

@[simp] theorem odd_interleave (s₁ s₂ : stream α) : odd (s₁ ⋈ s₂) = s₂ :=
ext $ λ n, nth_interleave_bit n s₁ s₂ tt

theorem ext_even_odd (he : even s₁ = even s₂) (ho : odd s₁ = odd s₂) : s₁ = s₂ :=
begin
  refine (ext $ λ n, bit_cases_on n $ λ b k, _),
  cases b,
  { have := congr_arg2 nth he (refl k), exact this },
  { have := congr_arg2 nth ho (refl k), exact this }
end

theorem interleave_even_odd (s : stream α) : even s ⋈ odd s = s :=
ext_even_odd (even_interleave _ _) (odd_interleave _ _)

@[simp] theorem even_tail (s : stream α) : even (tail s) = odd s := rfl

theorem odd_tail (s : stream α) : odd (tail s) = tail (even s) :=
ext $ λ n, by simp [nat.left_distrib, nat.mul_one]

@[simp] theorem even_cons (a : α) (s : stream α) : even (a :: s) = a :: odd s :=
ext_head_tail rfl $ by rw [← odd_tail, tail_cons, tail_cons]

@[simp] theorem odd_cons (a : α) (s : stream α) : odd (a :: s) = even s := rfl

theorem tail_interleave (s₁ s₂ : stream α) : tail (s₁ ⋈ s₂) = s₂ ⋈ (tail s₁) :=
ext_even_odd
  (by rw [even_tail, odd_interleave, even_interleave])
  (by rw [odd_tail, even_interleave, odd_interleave])

theorem interleave_tail_tail (s₁ s₂ : stream α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) :=
by rw [tail_interleave, tail_interleave]

theorem interleave_eq (s₁ s₂ : stream α) : s₁ ⋈ s₂ = head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂) :=
ext_head_tail rfl $ ext_head_tail rfl (interleave_tail_tail _ _).symm

theorem mem_of_mem_even : a ∈ even s → a ∈ s := λ ⟨n, h⟩, ⟨_, h⟩
theorem mem_of_mem_odd : a ∈ odd s → a ∈ s := λ ⟨n, h⟩, ⟨_, h⟩

theorem mem_interleave_left (s₂ : stream α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
λ ⟨n, h⟩, ⟨2 * n, by rw [h, nth_interleave_left]⟩

theorem mem_interleave_right (s₁ : stream α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
λ ⟨n, h⟩, ⟨2 * n + 1, by rw [h, nth_interleave_right]⟩

@[simp] theorem head_even (s : stream α) : head (even s) = head s := rfl

@[simp] theorem take_zero (s : stream α) : take 0 s = [] := rfl

@[simp] theorem take_succ (n : ℕ) (s : stream α) :
  take (succ n) s = head s :: take n (tail s) := rfl

@[simp] theorem length_take (n : ℕ) (s : stream α) : (take n s).length = n :=
by induction n generalizing s; simp *

theorem nth_take_succ : ∀ (n : ℕ) (s : stream α), list.nth (take (n + 1) s) n = some (nth s n)
| 0     s := rfl
| (n+1) s := by rw [take_succ, list.nth, nth_take_succ, nth_tail]

end stream

namespace list

open stream

@[simp] theorem nil_append_stream (s : stream α) : [] ++ₛ s = s := rfl

theorem cons_append_stream (a : α) (l : list α) (s : stream α) :
  (a::l) ++ₛ s = a :: (l ++ₛ s) :=
rfl

theorem append_append_stream :
  ∀ (l₁ l₂ : list α) (s : stream α), (l₁ ++ l₂) ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
| []               l₂ s := rfl
| (list.cons a l₁) l₂ s := by rw [list.cons_append, cons_append_stream, cons_append_stream,
                                  append_append_stream]

@[simp] theorem map_append_stream (f : α → β) :
  ∀ (l : list α) (s : stream α), (l ++ₛ s).map f = l.map f ++ₛ s.map f
| []     s := rfl
| (a::l) s := by rw [cons_append_stream, map_cons, stream.map_cons, cons_append_stream,
                     map_append_stream]

@[simp] theorem drop_append_stream : ∀ (l : list α) (s : stream α), (l ++ₛ s).drop l.length = s
| []     s := s.drop_zero
| (a::l) s := by rw [length_cons, add_one, drop_succ, cons_append_stream, stream.tail_cons,
                     drop_append_stream]

@[simp] theorem mem_append_stream : ∀ {l : list α} {s : stream α}, a ∈ l ++ₛ s ↔ a ∈ l ∨ a ∈ s
| []       s := (false_or _).symm
| (b :: l) s := by rw [cons_append_stream, mem_cons_iff, stream.mem_cons_iff, mem_append_stream,
                       or_assoc]

theorem mem_append_stream_right (l : list α) (h : a ∈ s) : a ∈ l ++ₛ s :=
mem_append_stream.2 (or.inr h)

theorem mem_append_stream_left {l : list α} (s : stream α) (h : a ∈ l) : a ∈ l ++ₛ s :=
mem_append_stream.2 (or.inl h)

theorem nth_append_stream (l : list α) (s : stream α) :
  (l ++ₛ s).nth n = if h : n < length l then l.nth_le n h else s.nth (n - length l) :=
begin
  induction l with a l ihl generalizing n,
  { rw [dif_neg, length, nat.sub_zero, nil_append_stream],
    exact nat.not_lt_zero _ },
  { rw [cons_append_stream],
    cases n,
    { rw [stream.nth_zero, stream.head_cons, dif_pos, nth_le],
      exact nat.succ_pos _ },
    { rw [nth_cons_succ, ihl],
      simp only [length, iff.intro nat.lt_of_succ_lt_succ nat.succ_lt_succ, nth_le,
        nat.succ_sub_succ],
      congr } }
end

theorem nth_append_stream_of_lt_length {l : list α} (h : n < length l) (s : stream α) :
  (l ++ₛ s).nth n = l.nth_le n h :=
(nth_append_stream _ _).trans (dif_pos _)

theorem nth_append_stream_of_length_le {l : list α} (h : length l ≤ n) (s : stream α) :
  (l ++ₛ s).nth n = s.nth (n - length l) :=
(nth_append_stream _ _).trans (dif_neg $ not_lt.2 h)

end list

namespace stream

theorem append_stream_head_tail (s : stream α) : [head s] ++ₛ tail s = s := s.cons_head_tail

theorem append_take_drop (s : stream α) (n : ℕ) : take n s ++ₛ drop n s = s :=
begin
  induction n with n ihn generalizing s,
  { exact s.drop_zero },
  { rw [take_succ, drop_succ, list.cons_append_stream, ihn, cons_head_tail] }
end

/-- Take theorem reduces a proof of equality of infinite streams to an induction over all their
finite approximations. -/
theorem take_theorem (s₁ s₂ : stream α) (h : ∀ n, take n s₁ = take n s₂) : s₁ = s₂ :=
ext $ λ n, by rw [← option.some_inj, ← nth_take_succ, h, nth_take_succ]

theorem cycle_eq (l : list α) (h : l ≠ []) : cycle l h = l ++ₛ cycle l h :=
begin
  ext n,
  cases lt_or_le n l.length with h h,
  { simp only [nth_cycle, list.nth_append_stream_of_lt_length h, nat.mod_eq_of_lt h] },
  { simp only [nth_cycle, list.nth_append_stream_of_length_le h, ← nat.mod_eq_sub_mod h] }
end

@[simp] theorem mem_cycle {l : list α} (hl : l ≠ []) : a ∈ cycle l hl ↔ a ∈ l  :=
⟨λ ⟨n, hn⟩, hn.symm ▸ l.nth_le_mem _ _, λ h, (cycle_eq l hl).symm ▸ list.mem_append_stream_left _ h⟩

@[simp] theorem cycle_singleton (a : α) (h : [a] ≠ [] := list.cons_ne_nil _ _) :
  cycle [a] h = pure a :=
coinduction rfl (λ β fr ch, by rwa [cycle_eq, ← cons_self_pure])

theorem tails_eq (s : stream α) : tails s = s :: tails (tail s) :=
iterate_tail s ▸ iterate_tail (tail s) ▸ iterate_eq _ _

theorem inits_eq (s : stream α) : inits s = [] :: map (list.cons (head s)) (inits (tail s)) :=
ext_head_tail rfl $ ext $ λ n, take_succ _ _

theorem zip_inits_tails (s : stream α) : zip (++ₛ) (inits s) (tails s) = pure s :=
ext $ append_take_drop _

@[simp] theorem id_apply (s : stream α) : pure id ⊛ s = s := ext $ λ _, rfl

theorem composition (g : stream (β → δ)) (f : stream (α → β)) (s : stream α) :
  pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) := rfl
theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) := rfl
theorem interchange (fs : stream (α → β)) (a : α) :
  fs ⊛ pure a = pure (λ f : α → β, f a) ⊛ fs := rfl
@[simp] theorem pure_apply (f : α → β) (s : stream α) : pure f ⊛ s = map f s := rfl

theorem nats_eq : nats = 0 :: map succ nats := ext_head_tail rfl rfl

end stream
