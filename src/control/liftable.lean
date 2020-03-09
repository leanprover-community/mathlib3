/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.equiv.basic
import tactic

/-!
# Liftable Class

Some functors such as `option` and `list` are universe polymorphic. Unlike
type polymorphism where `option α` is a function application and reasoning and
generalizations that apply to functions can be used, `option.{u}` and `option.{v}`
are not one function applied to two universe names but one polymorphic definition
instantiated twice. This means that whatever works on `option.{u}` is hard
to transport over to `option.{v}`. `liftable` is an attempt at improving the situation.

`liftable option.{u} option.{v}` gives us a generic and composable way to use
`option.{u}` in a context that requires `option.{v}`. It is often used in tandem with
`ulift` but the two are purposefully decoupled.


## Main definitions
  * `liftable` class

## Tags

universe polymorphism functor

-/

universes u₀ u₁ v₀ v₁ v₂ w w₀ w₁

/-- Given a universe polymorphic functor `M.{u}`, this class helps move from
`M.{u}` to `M.{v}` and back -/
class liftable (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) :=
(congr [] {α β} : α ≃ β → f α ≃ g β)

namespace liftable

/-- The most common practical use `liftable` (together with `up`), this function takes `x : M.{u} α` and lifts it
to M.{max u v} (ulift.{v} α) -/
@[reducible]
def up {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} : f α → g (ulift α) :=
(liftable.congr f g equiv.ulift.symm).to_fun

/-- The most common practical use of `liftable` (together with `up`), this function takes `x : M.{max u v} (ulift.{v} α)`
and lowers it to `M.{u} α` -/
@[reducible]
def down {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} : g (ulift α) → f α :=
(liftable.congr f g equiv.ulift.symm).inv_fun

/-- convenient shortcut to avoid manipulating `ulift` -/
def adapt_up {F : Type u₀ → Type u₁} {G : Type (max u₀ v₀) → Type v₁}
  [liftable F G] [monad G] {α β}
  (x : F α) (f : α → G β) : G β :=
up x >>= f ∘ ulift.down

/-- convenient shortcut to avoid manipulating `ulift` -/
def adapt_down {F : Type (max u₀ v₀) → Type u₁} {G : Type v₀ → Type v₁}
  [L : liftable G F] [monad F] {α β}
  (x : F α) (f : α → G β) : G β :=
@down.{v₀ v₁ (max u₀ v₀)} G F L β $ x >>= @up.{v₀ v₁ (max u₀ v₀)} G F L β ∘ f

@[simp]
lemma up_down  {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} (x : g (ulift α)) : up (down x : f α) = x := (liftable.congr f g equiv.ulift.symm).right_inv _

@[simp]
lemma down_up  {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} (x : f α) : down (up x : g _) = x := (liftable.congr f g equiv.ulift.symm).left_inv _

end liftable

open ulift

instance : liftable id id :=
{ congr := λ α β F, F }

/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
def state_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ σ₁ : Type u₀} {α₂ σ₂ : Type u₁} (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) :
  state_t σ₁ m₁ α₁ ≃ state_t σ₂ m₂ α₂ :=
{ to_fun := λ ⟨f⟩, ⟨F f⟩,
  inv_fun := λ ⟨f⟩, ⟨F.symm f⟩,
  left_inv := λ ⟨f⟩, congr_arg state_t.mk $ F.left_inv _,
  right_inv := λ ⟨f⟩, congr_arg state_t.mk $ F.right_inv _ }

/-- for specific state types, this function helps to create a liftable instance -/
def state_t.liftable' {s : Type u₀} {s' : Type u₁}
  {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁}
  [liftable m m']
  (F : s ≃ s') :
  liftable (state_t s m) (state_t s' m') :=
{ congr :=
    λ α β G, state_t.equiv $ equiv.Pi_congr F $
      λ _, liftable.congr _ _ $ equiv.prod_congr G F }

instance {s m m'}
  [liftable m m'] :
  liftable (state_t s m) (state_t (ulift s) m') :=
state_t.liftable' equiv.ulift.symm

/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
def reader_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ ρ₁ : Type u₀} {α₂ ρ₂ : Type u₁} (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) :
  reader_t ρ₁ m₁ α₁ ≃ reader_t ρ₂ m₂ α₂ :=
{ to_fun := λ ⟨f⟩, ⟨F f⟩,
  inv_fun := λ ⟨f⟩, ⟨F.symm f⟩,
  left_inv := λ ⟨f⟩, congr_arg reader_t.mk $ F.left_inv _,
  right_inv := λ ⟨f⟩, congr_arg reader_t.mk $ F.right_inv _ }

/-- for specific reader monads, this function helps to create a liftable instance -/
def reader_t.liftable' {s s' m m'}
  [liftable m m']
  (F : s ≃ s') :
  liftable (reader_t s m) (reader_t s' m') :=
{ congr :=
    λ α β G, reader_t.equiv $ equiv.Pi_congr F $
      λ _, liftable.congr _ _ G }

instance {s m m'} [liftable m m'] : liftable (reader_t s m) (reader_t (ulift s) m') :=
reader_t.liftable' equiv.ulift.symm
