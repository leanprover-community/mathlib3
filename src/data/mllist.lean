/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carnerio, Keeley Hoek, Scott Morrison

Monadic lazy lists.

The inductive construction is not allowed outside of meta (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.

As we're in meta anyway, we don't bother with proofs about these constructions.
-/

universes u v

meta inductive mllist (m : Type u → Type u) (α : Type u) : Type u
| nil {} : mllist
| cons : α → m mllist → mllist

namespace mllist

meta def empty {m} [monad m] {α : Type u} : mllist m α → bool
| nil := ff
| (cons _ _) := tt

meta def fix {m : Type u → Type u} [alternative m]
  {α} (f : α → m α) : α → m (mllist m α)
| x := (λ a, cons a (fix a)) <$> f x <|> pure nil

meta def of_list {m} [monad m] {α : Type u} : list α → mllist m α
| [] := nil
| (h :: t) := cons h (pure (of_list t))

meta def m_of_list {m} [monad m] {α : Type u} : list (m α) → m (mllist m α)
| [] := return nil
| (h :: t) := do a ← h, return (cons a (m_of_list t))

meta def force {m} [monad m] {α} : mllist m α → m (list α)
| nil := pure []
| (cons a l) := list.cons a <$> (l >>= force)

meta def map {m} [monad m] {α β : Type u} (f : α → β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, return (cons (f a) (map r))

meta def mmap {m} [monad m] [alternative m] {α β : Type u} (f : α → m β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, b ← f a, return (cons b (mmap r))

meta def filter {m} [monad m] {α : Type u} (p : α → Prop) [decidable_pred p] : mllist m α → m (mllist m α)
| nil := pure nil
| (cons a l) := do r ← l, if p a then return (cons a (filter r)) else filter r

meta def mfilter {m} [monad m] [alternative m] {α β : Type} (p : α → m β) : mllist m α → m (mllist m α)
| nil := pure nil
| (cons a l) := do r ← l, (p a >> return (cons a (mfilter r))) <|> mfilter r

meta def filter_map {m} [monad m] {α β : Type u} (f : α → option β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, match f a with
  | (some b) := return (cons b (filter_map r))
  | none := filter_map r
  end

meta def mfilter_map {m} [monad m] [alternative m] {α β : Type u} (f : α → m β) : mllist m α → m (mllist m β)
| nil := pure nil
| (cons a l) := do r ← l, (f a >>= (λ b, return (cons b (mfilter_map r)))) <|> mfilter_map r

meta def join {m} [monad m] {α : Type u} : mllist m (mllist m α) → m (mllist m α)
| nil := pure nil
| (cons nil l) := do r ← l, join r
| (cons (cons a m) l) := do n ← m, return (cons a (join (cons n l)))

meta def enum_from {m} [monad m] {α : Type u} : ℕ → mllist m α → m (mllist m (ℕ × α))
| _ nil := return nil
| n (cons a l) := do r ← l, return (cons (n, a) (enum_from (n + 1) r))

meta def enum {m} [monad m] {α : Type u} : mllist m α → m (mllist m (ℕ × α)) := enum_from 0

meta def concat {m} [monad m] {α : Type u} : mllist m α → α → m (mllist m α)
| L a := (mllist.of_list [L, mllist.of_list [a]]).join

end mllist
