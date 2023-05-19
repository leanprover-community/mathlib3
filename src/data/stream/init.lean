/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import data.stream.defs
import tactic.ext
import logic.function.basic

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.  -/

open nat function option

universes u v w

namespace stream
variables {α : Type u} {β : Type v} {δ : Type w}

instance {α} [inhabited α] : inhabited (stream α) :=
⟨stream.const default⟩

protected theorem eta (s : stream α) : head s :: tail s = s :=
funext (λ i, begin cases i; refl end)

@[simp] theorem nth_zero_cons (a : α) (s : stream α) : nth (a :: s) 0 = a := rfl

theorem head_cons (a : α) (s : stream α) : head (a :: s) = a := rfl

theorem tail_cons (a : α) (s : stream α) : tail (a :: s) = s := rfl

theorem tail_drop (n : nat) (s : stream α) : tail (drop n s) = drop n (tail s) :=
funext (λ i, begin unfold tail drop, simp [nth, nat.add_comm, nat.add_left_comm] end)

theorem nth_drop (n m : nat) (s : stream α) : nth (drop m s) n = nth s (n + m) := rfl

theorem tail_eq_drop (s : stream α) : tail s = drop 1 s := rfl

theorem drop_drop (n m : nat) (s : stream α) : drop n (drop m s) = drop (n+m) s :=
funext (λ i, begin unfold drop, rw nat.add_assoc end)

theorem nth_succ (n : nat) (s : stream α) : nth s (succ n) = nth (tail s) n := rfl

@[simp] lemma nth_succ_cons (n : nat) (s : stream α) (x : α) : nth (x :: s) n.succ = nth s n := rfl

theorem drop_succ (n : nat) (s : stream α) : drop (succ n) s = drop n (tail s) := rfl

@[simp] lemma head_drop {α} (a : stream α) (n : ℕ) : (a.drop n).head = a.nth n :=
by simp only [drop, head, nat.zero_add, stream.nth]

@[ext] protected theorem ext {s₁ s₂ : stream α} : (∀ n, nth s₁ n = nth s₂ n) → s₁ = s₂ :=
assume h, funext h

lemma cons_injective2 : function.injective2 (cons : α → stream α → stream α) :=
λ x y s t h, ⟨by rw [←nth_zero_cons x s, h, nth_zero_cons],
  stream.ext (λ n, by rw [←nth_succ_cons n _ x, h, nth_succ_cons])⟩

lemma cons_injective_left (s : stream α) : function.injective (λ x, cons x s) :=
cons_injective2.left _

lemma cons_injective_right (x : α) : function.injective (cons x) :=
cons_injective2.right _

theorem all_def (p : α → Prop) (s : stream α) : all p s = ∀ n, p (nth s n) := rfl

theorem any_def (p : α → Prop) (s : stream α) : any p s = ∃ n, p (nth s n) := rfl

theorem mem_cons (a : α) (s : stream α) : a ∈ (a::s) :=
exists.intro 0 rfl

theorem mem_cons_of_mem {a : α} {s : stream α} (b : α) : a ∈ s → a ∈ b :: s :=
assume ⟨n, h⟩,
exists.intro (succ n) (by rw [nth_succ, tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : α} {s : stream α} : a ∈ b::s → a = b ∨ a ∈ s :=
assume ⟨n, h⟩,
begin
  cases n with n',
  { left, exact h },
  { right, rw [nth_succ, tail_cons] at h, exact ⟨n', h⟩ }
end

theorem mem_of_nth_eq {n : nat} {s : stream α} {a : α} : a = nth s n → a ∈ s :=
assume h, exists.intro n h

section map
variable (f : α → β)

theorem drop_map (n : nat) (s : stream α) : drop n (map f s) = map f (drop n s) :=
stream.ext (λ i, rfl)

theorem nth_map (n : nat) (s : stream α) : nth (map f s) n = f (nth s n) := rfl

theorem tail_map (s : stream α) : tail (map f s) = map f (tail s) :=
begin rw tail_eq_drop, refl end

theorem head_map (s : stream α) : head (map f s) = f (head s) := rfl

theorem map_eq (s : stream α) : map f s = f (head s) :: map f (tail s) :=
by rw [← stream.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : stream α) : map f (a :: s) = f a :: map f s :=
begin rw [← stream.eta (map f (a :: s)), map_eq], refl end

theorem map_id (s : stream α) : map id s = s := rfl

theorem map_map (g : β → δ) (f : α → β) (s : stream α) : map g (map f s) = map (g ∘ f) s := rfl

theorem map_tail (s : stream α) : map f (tail s) = tail (map f s) := rfl

theorem mem_map {a : α} {s : stream α} : a ∈ s → f a ∈ map f s :=
assume ⟨n, h⟩,
exists.intro n (by rw [nth_map, h])

theorem exists_of_mem_map {f} {b : β} {s : stream α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
assume ⟨n, h⟩, ⟨nth s n, ⟨n, rfl⟩, h.symm⟩
end map

section zip
variable (f : α → β → δ)

theorem drop_zip (n : nat) (s₁ : stream α) (s₂ : stream β) :
  drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
stream.ext (λ i, rfl)

theorem nth_zip (n : nat) (s₁ : stream α) (s₂ : stream β) :
  nth (zip f s₁ s₂) n = f (nth s₁ n) (nth s₂ n) := rfl

theorem head_zip (s₁ : stream α) (s₂ : stream β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) := rfl

theorem tail_zip (s₁ : stream α) (s₂ : stream β) :
  tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) := rfl

theorem zip_eq (s₁ : stream α) (s₂ : stream β) :
  zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) :=
begin rw [← stream.eta (zip f s₁ s₂)], refl end

@[simp] lemma nth_enum (s : stream α) (n : ℕ) : nth (enum s) n = (n, s.nth n) := rfl

lemma enum_eq_zip (s : stream α) : enum s = zip prod.mk nats s := rfl

end zip

theorem mem_const (a : α) : a ∈ const a :=
exists.intro 0 rfl

theorem const_eq (a : α) : const a = a :: const a :=
begin
  apply stream.ext, intro n,
  cases n; refl
end

theorem tail_const (a : α) : tail (const a) = const a :=
suffices tail (a :: const a) = const a, by rwa [← const_eq] at this, rfl

theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) := rfl

theorem nth_const (n : nat) (a : α) : nth (const a) n = a := rfl

theorem drop_const (n : nat) (a : α) : drop n (const a) = const a :=
stream.ext (λ i, rfl)

theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a := rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) :=
begin
  funext n,
  induction n with n' ih,
  { refl },
  { unfold tail iterate,
    unfold tail iterate at ih,
    rw add_one at ih, dsimp at ih,
    rw add_one, dsimp, rw ih }
end

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a :: iterate f (f a) :=
begin
  rw [← stream.eta (iterate f a)],
  rw tail_iterate, refl
end

theorem nth_zero_iterate (f : α → α) (a : α) : nth (iterate f a) 0 = a := rfl

theorem nth_succ_iterate (n : nat) (f : α → α) (a : α) :
  nth (iterate f a) (succ n) = nth (iterate f (f a)) n :=
by rw [nth_succ, tail_iterate]

section bisim
  variable (R : stream α → stream α → Prop)
  local infix ` ~ `:50 := R

  def is_bisimulation := ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

  theorem nth_of_bisim (bisim : is_bisimulation R) :
    ∀ {s₁ s₂} n, s₁ ~ s₂ → nth s₁ n = nth s₂ n ∧ drop (n+1) s₁ ~ drop (n+1) s₂
  | s₁ s₂ 0     h := bisim h
  | s₁ s₂ (n+1) h :=
    match bisim h with
    | ⟨h₁, trel⟩ := nth_of_bisim n trel
    end

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  λ s₁ s₂ r, stream.ext (λ n, and.elim_left (nth_of_bisim R bisim n r))
end bisim

theorem bisim_simple (s₁ s₂ : stream α) :
  head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ :=
assume hh ht₁ ht₂, eq_of_bisim
  (λ s₁ s₂, head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
  (λ s₁ s₂ ⟨h₁, h₂, h₃⟩,
    begin
      constructor, exact h₁, rw [← h₂, ← h₃], repeat { constructor }; assumption
    end)
  (and.intro hh (and.intro ht₁ ht₂))

theorem coinduction {s₁ s₂ : stream α} :
  head s₁ = head s₂ → (∀ (β : Type u) (fr : stream α → β), fr s₁ = fr s₂ →
    fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
assume hh ht,
  eq_of_bisim
    (λ s₁ s₂, head s₁ = head s₂ ∧ ∀ (β : Type u) (fr : stream α → β), fr s₁ = fr s₂ →
      fr (tail s₁) = fr (tail s₂))
    (λ s₁ s₂ h,
      have h₁ : head s₁ = head s₂,               from and.elim_left h,
      have h₂ : head (tail s₁) = head (tail s₂), from and.elim_right h α (@head α) h₁,
      have h₃ : ∀ (β : Type u) (fr : stream α → β),
        fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)),
      from λ β fr, and.elim_right h β (λ s, fr (tail s)),
      and.intro h₁ (and.intro h₂ h₃))
    (and.intro hh ht)

theorem iterate_id (a : α) : iterate id a = const a :=
coinduction
  rfl
  (λ β fr ch, begin rw [tail_iterate, tail_const], exact ch end)

local attribute [reducible] stream
theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) :=
begin
  funext n,
  induction n with n' ih,
  { refl },
  { unfold map iterate nth, dsimp,
    unfold map iterate nth at ih, dsimp at ih,
    rw ih }
end

section corec
theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) := rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) :=
begin rw [corec_def, map_eq, head_iterate, tail_iterate], refl end

theorem corec_id_id_eq_const (a : α) : corec id id a = const a :=
by rw [corec_def, map_id, iterate_id]

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a := rfl
end corec

section corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
corec_eq _ _ _

end corec'

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) :=
begin unfold unfolds, rw [corec_eq] end

theorem nth_unfolds_head_tail : ∀ (n : nat) (s : stream α), nth (unfolds head tail s) n = nth s n :=
begin
  intro n, induction n with n' ih,
  { intro s, refl },
  { intro s, rw [nth_succ, nth_succ, unfolds_eq, tail_cons, ih] }
end

theorem unfolds_head_eq : ∀ (s : stream α), unfolds head tail s = s :=
λ s, stream.ext (λ n, nth_unfolds_head_tail n s)

theorem interleave_eq (s₁ s₂ : stream α) : s₁ ⋈ s₂ = head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂) :=
begin
  unfold interleave corec_on, rw corec_eq, dsimp, rw corec_eq, refl
end

theorem tail_interleave (s₁ s₂ : stream α) : tail (s₁ ⋈ s₂) = s₂ ⋈ (tail s₁) :=
begin unfold interleave corec_on, rw corec_eq, refl end

theorem interleave_tail_tail (s₁ s₂ : stream α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) :=
begin rw [interleave_eq s₁ s₂], refl end

theorem nth_interleave_left : ∀ (n : nat) (s₁ s₂ : stream α), nth (s₁ ⋈ s₂) (2 * n) = nth s₁ n
| 0        s₁ s₂ := rfl
| (succ n) s₁ s₂ :=
  begin
    change nth (s₁ ⋈ s₂) (succ (succ (2*n))) = nth s₁ (succ n),
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_left],
    refl
  end

theorem nth_interleave_right : ∀ (n : nat) (s₁ s₂ : stream α), nth (s₁ ⋈ s₂) (2*n+1) = nth s₂ n
| 0        s₁ s₂ := rfl
| (succ n) s₁ s₂ :=
  begin
    change nth (s₁ ⋈ s₂) (succ (succ (2*n+1))) = nth s₂ (succ n),
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_right],
    refl
  end

theorem mem_interleave_left {a : α} {s₁ : stream α} (s₂ : stream α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
assume ⟨n, h⟩,
exists.intro (2*n) (by rw [h, nth_interleave_left])

theorem mem_interleave_right {a : α} {s₁ : stream α} (s₂ : stream α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
assume ⟨n, h⟩,
exists.intro (2*n+1) (by rw [h, nth_interleave_right])

theorem odd_eq (s : stream α) : odd s = even (tail s) := rfl

theorem head_even (s : stream α) : head (even s) = head s := rfl

theorem tail_even (s : stream α) : tail (even s) = even (tail (tail s)) :=
begin unfold even, rw corec_eq, refl end

theorem even_cons_cons (a₁ a₂ : α) (s : stream α) : even (a₁ :: a₂ :: s) = a₁ :: even s :=
begin unfold even, rw corec_eq, refl end

theorem even_tail (s : stream α) : even (tail s) = odd s := rfl

theorem even_interleave (s₁ s₂ : stream α) : even (s₁ ⋈ s₂) = s₁ :=
eq_of_bisim
  (λ s₁' s₁, ∃ s₂, s₁' = even (s₁ ⋈ s₂))
  (λ s₁' s₁ ⟨s₂, h₁⟩,
    begin
      rw h₁,
      constructor,
       {refl},
       {exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩}
    end)
  (exists.intro s₂ rfl)

theorem interleave_even_odd (s₁ : stream α) : even s₁ ⋈ odd s₁ = s₁ :=
eq_of_bisim
  (λ s' s, s' = even s ⋈ odd s)
  (λ s' s (h : s' = even s ⋈ odd s),
    begin
      rw h, constructor,
       {refl},
       {simp [odd_eq, odd_eq, tail_interleave, tail_even]}
    end)
  rfl

theorem nth_even : ∀ (n : nat) (s : stream α), nth (even s) n = nth s (2*n)
| 0        s := rfl
| (succ n) s :=
  begin
    change nth (even s) (succ n) = nth s (succ (succ (2 * n))),
    rw [nth_succ, nth_succ, tail_even, nth_even], refl
  end

theorem nth_odd : ∀ (n : nat) (s : stream α), nth (odd s) n = nth s (2 * n + 1) :=
λ n s, begin rw [odd_eq, nth_even], refl end

theorem mem_of_mem_even (a : α) (s : stream α) : a ∈ even s → a ∈ s :=
assume ⟨n, h⟩,
exists.intro (2*n) (by rw [h, nth_even])

theorem mem_of_mem_odd (a : α) (s : stream α) : a ∈ odd s → a ∈ s :=
assume ⟨n, h⟩,
exists.intro (2*n+1) (by rw [h, nth_odd])

theorem nil_append_stream (s : stream α) : append_stream [] s = s := rfl

theorem cons_append_stream (a : α) (l : list α) (s : stream α) :
  append_stream (a::l) s = a :: append_stream l s := rfl

theorem append_append_stream :
  ∀ (l₁ l₂ : list α) (s : stream α), (l₁ ++ l₂) ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
| []               l₂ s := rfl
| (list.cons a l₁) l₂ s := by rw [list.cons_append, cons_append_stream, cons_append_stream,
                                  append_append_stream]

theorem map_append_stream (f : α → β) :
  ∀ (l : list α) (s : stream α), map f (l ++ₛ s) = list.map f l ++ₛ map f s
| []              s := rfl
| (list.cons a l) s := by rw [cons_append_stream, list.map_cons, map_cons, cons_append_stream,
                              map_append_stream]

theorem drop_append_stream : ∀ (l : list α) (s : stream α), drop l.length (l ++ₛ s) = s
| []              s := by refl
| (list.cons a l) s := by rw [list.length_cons, add_one, drop_succ, cons_append_stream, tail_cons,
                              drop_append_stream]

theorem append_stream_head_tail (s : stream α) : [head s] ++ₛ tail s = s :=
by rw [cons_append_stream, nil_append_stream, stream.eta]

theorem mem_append_stream_right : ∀ {a : α} (l : list α) {s : stream α}, a ∈ s → a ∈ l ++ₛ s
| a []              s h := h
| a (list.cons b l) s h :=
  have ih : a ∈ l ++ₛ s, from mem_append_stream_right l h,
  mem_cons_of_mem _ ih

theorem mem_append_stream_left : ∀ {a : α} {l : list α} (s : stream α), a ∈ l → a ∈ l ++ₛ s
| a []     s h := absurd h (list.not_mem_nil _)
| a (list.cons b l) s h :=
  or.elim (list.eq_or_mem_of_mem_cons h)
    (λ (aeqb : a = b), exists.intro 0 aeqb)
    (λ (ainl : a ∈ l), mem_cons_of_mem b (mem_append_stream_left s ainl))

@[simp] theorem take_zero (s : stream α) : take 0 s = [] := rfl

@[simp] theorem take_succ (n : nat) (s : stream α) :
  take (succ n) s = head s :: take n (tail s) := rfl

@[simp] theorem length_take (n : ℕ) (s : stream α) : (take n s).length = n :=
by induction n generalizing s; simp *

theorem nth_take_succ : ∀ (n : nat) (s : stream α), list.nth (take (succ n) s) n = some (nth s n)
| 0     s := rfl
| (n+1) s := begin rw [take_succ, add_one, list.nth, nth_take_succ], refl end

theorem append_take_drop :
  ∀ (n : nat) (s : stream α), append_stream (take n s) (drop n s) = s :=
begin
  intro n,
  induction n with n' ih,
  { intro s, refl },
  { intro s, rw [take_succ, drop_succ, cons_append_stream, ih (tail s), stream.eta] }
end

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : stream α) : (∀ (n : nat), take n s₁ = take n s₂) → s₁ = s₂ :=
begin
  intro h, apply stream.ext, intro n,
  induction n with n ih,
  { have aux := h 1, simp [take] at aux, exact aux },
  { have h₁ : some (nth s₁ (succ n)) = some (nth s₂ (succ n)),
    { rw [← nth_take_succ, ← nth_take_succ, h (succ (succ n))] },
    injection h₁ }
end

protected lemma cycle_g_cons (a : α) (a₁ : α) (l₁ : list α) (a₀ : α) (l₀ : list α) :
              stream.cycle_g (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) := rfl

theorem cycle_eq : ∀ (l : list α) (h : l ≠ []), cycle l h = l ++ₛ cycle l h
| []              h := absurd rfl h
| (list.cons a l) h :=
  have gen : ∀ l' a', corec stream.cycle_f stream.cycle_g (a', l', a, l) =
    (a' :: l') ++ₛ corec stream.cycle_f stream.cycle_g (a, l, a, l),
    begin
      intro l',
      induction l' with a₁ l₁ ih,
        {intros, rw [corec_eq], refl},
        {intros, rw [corec_eq, stream.cycle_g_cons, ih a₁], refl}
    end,
  gen l a

theorem mem_cycle {a : α} {l : list α} : ∀ (h : l ≠ []), a ∈ l → a ∈ cycle l h :=
assume h ainl, begin rw [cycle_eq], exact mem_append_stream_left _ ainl end

theorem cycle_singleton (a : α) (h : [a] ≠ []) : cycle [a] h = const a :=
coinduction
  rfl
  (λ β fr ch, by rwa [cycle_eq, const_eq])

theorem tails_eq (s : stream α) : tails s = tail s :: tails (tail s) :=
by unfold tails; rw [corec_eq]; refl

theorem nth_tails : ∀ (n : nat) (s : stream α), nth (tails s) n = drop n (tail s) :=
begin
  intro n, induction n with n' ih,
  { intros, refl },
  { intro s, rw [nth_succ, drop_succ, tails_eq, tail_cons, ih] }
end

theorem tails_eq_iterate (s : stream α) : tails s = iterate tail (tail s) := rfl

theorem inits_core_eq (l : list α) (s : stream α) :
  inits_core l s = l :: inits_core (l ++ [head s]) (tail s) :=
begin unfold inits_core corec_on, rw [corec_eq], refl end

theorem tail_inits (s : stream α) :
  tail (inits s) = inits_core [head s, head (tail s)] (tail (tail s)) :=
begin unfold inits, rw inits_core_eq, refl end

theorem inits_tail (s : stream α) :
  inits (tail s) = inits_core [head (tail s)] (tail (tail s)) := rfl

theorem cons_nth_inits_core : ∀ (a : α) (n : nat) (l : list α) (s : stream α),
                                 a :: nth (inits_core l s) n = nth (inits_core (a::l) s) n :=
begin
  intros a n,
  induction n with n' ih,
  { intros, refl },
  { intros l s, rw [nth_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a::l) s], refl }
end

theorem nth_inits : ∀ (n : nat) (s : stream α), nth (inits s) n = take (succ n) s  :=
begin
  intro n, induction n with n' ih,
  { intros, refl },
  { intros, rw [nth_succ, take_succ, ← ih, tail_inits, inits_tail, cons_nth_inits_core] }
end

theorem inits_eq (s : stream α) : inits s = [head s] :: map (list.cons (head s)) (inits (tail s)) :=
begin
  apply stream.ext, intro n,
  cases n,
  { refl },
  { rw [nth_inits, nth_succ, tail_cons, nth_map, nth_inits], refl }
end

theorem zip_inits_tails (s : stream α) : zip append_stream (inits s) (tails s) = const s :=
begin
  apply stream.ext, intro n,
  rw [nth_zip, nth_inits, nth_tails, nth_const, take_succ,
      cons_append_stream, append_take_drop, stream.eta]
end

theorem identity (s : stream α) : pure id ⊛ s = s := rfl
theorem composition (g : stream (β → δ)) (f : stream (α → β)) (s : stream α) :
  pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) := rfl
theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) := rfl
theorem interchange (fs : stream (α → β)) (a : α) :
  fs ⊛ pure a = pure (λ f : α → β, f a) ⊛ fs := rfl
theorem map_eq_apply (f : α → β) (s : stream α) : map f s = pure f ⊛ s := rfl

theorem nth_nats (n : nat) : nth nats n = n := rfl

theorem nats_eq : nats = 0 :: map succ nats :=
begin
  apply stream.ext, intro n,
  cases n, refl, rw [nth_succ], refl
end

end stream
