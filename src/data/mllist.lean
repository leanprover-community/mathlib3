/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carnerio, Keeley Hoek, Scott Morrison

Monadic lazy lists.

The inductive construction is not allowed outside of meta (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.

As we're in meta anyway, we don't bother with proofs about these constructions.
-/
import data.option.basic
universes u v

meta inductive mllist (m : Type u → Type u) (α : Type u) : Type u
| nil {} : mllist
| cons : m (option α × mllist) → mllist

namespace mllist

variables {m : Type u → Type u}

meta def fix {m : Type u → Type u} [alternative m]
  {α} (f : α → m α) : α → mllist m α
| x := cons $ (λ a, (some x, fix a)) <$> f x <|> pure (some x, nil)

variables [monad m]

meta def uncons {α : Type u} : mllist m α → m (option (α × mllist m α))
| nil := pure none
| (cons l) := do (x,xs) ← l,
                 some x ← return x | uncons xs,
                 return (x,xs)

meta def empty {α : Type u} (xs : mllist m α) : m (ulift bool) :=
(ulift.up ∘ option.is_some) <$> uncons xs

meta def of_list {α : Type u} : list α → mllist m α
| [] := nil
| (h :: t) := cons (pure (h, of_list t))

meta def m_of_list {α : Type u} : list (m α) → mllist m α
| [] := nil
| (h :: t) := cons ((λ x, (x, m_of_list t)) <$> some <$> h)

meta def force {α} : mllist m α → m (list α)
| nil := pure []
| (cons l) :=
  do (x,xs) ← l,
     some x ← pure x | force xs,
     (::) x <$> (force xs)

meta def take {α} : mllist m α → ℕ → m (list α)
| nil _ := pure []
| _ 0 := pure []
| (cons l) (n+1) :=
  do (x,xs) ← l,
     some x ← pure x | take xs n,
     (::) x <$> (take xs n)

meta def map {α β : Type u} (f : α → β) : mllist m α → mllist m β
| nil := nil
| (cons l) := cons $ do (x,xs) ← l, pure (f <$> x, map xs)

meta def mmap {α β : Type u} (f : α → m β) : mllist m α → mllist m β
| nil := nil
| (cons l) :=
cons $ do (x,xs) ← l,
          b ← x.traverse f,
          return (b, mmap xs)

meta def filter {α : Type u} (p : α → Prop) [decidable_pred p] : mllist m α → mllist m α
| nil := nil
| (cons l) :=
cons $ do (a,r) ← l ,
          some a ← return a | return (none, filter r),
          return (if p a then some a else none, filter r)

meta def mfilter [alternative m] {α β : Type u} (p : α → m β) : mllist m α → mllist m α
| nil := nil
| (cons l) :=
cons $ do (a,r) ← l,
          some a ← return a | return (none, mfilter r),
          (p a >> return (a, mfilter r)) <|> return (none , mfilter r)

meta def filter_map {α β : Type u} (f : α → option β) : mllist m α → mllist m β
| nil := nil
| (cons l) :=
cons $ do (a,r) ← l,
          some a ← return a | return (none, filter_map r),
          match f a with
          | (some b) := return (some b, filter_map r)
          | none := return (none, filter_map r)
          end

meta def mfilter_map [alternative m] {α β : Type u} (f : α → m β) : mllist m α → mllist m β
| nil := nil
| (cons l) :=
cons $ do (a,r) ← l,
          some a ← return a | return (none, mfilter_map r),
          (f a >>= (λ b, return (some b, mfilter_map r))) <|> return (none, mfilter_map r)

meta def append {α : Type u} : mllist m α → mllist m α → mllist m α
| nil ys := ys
| (cons xs) ys :=
cons $ do (x,xs) ← xs,
          return (x, append xs ys)

meta def join {α : Type u} : mllist m (mllist m α) → mllist m α
| nil := nil
| (cons l) :=
cons $ do (xs,r) ← l,
       some xs ← return xs | return (none, join r),
       match xs with
       | nil := return (none, join r)
       | cons m := do (a,n) ← m, return (a, join (cons $ return (n, r)))
       end

meta def enum_from {α : Type u} : ℕ → mllist m α → mllist m (ℕ × α)
| _ nil := nil
| n (cons l) :=
cons $ do (a,r) ← l,
          some a ← return a | return (none, enum_from n r),
          return ((n, a), (enum_from (n + 1) r))

meta def enum {α : Type u} : mllist m α → mllist m (ℕ × α) := enum_from 0

meta def concat {α : Type u} : mllist m α → α → mllist m α
| L a := (mllist.of_list [L, mllist.of_list [a]]).join

meta def bind_ {α β : Type u} : mllist m α → (α → mllist m β) → mllist m β
| nil f := nil
| (cons ll) f :=
cons $ do (x,xs) ← ll,
          some x ← return x | return (none, bind_ xs f),
          return (none, append (f x) (bind_ xs f))

meta def monad_lift {α} (x : m α) : mllist m α := cons $ (flip prod.mk nil ∘ some) <$> x

end mllist
