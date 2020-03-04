
import data.equiv.basic
import tactic

universes u₀ u₁ v₀ v₁ v₂ w w₀ w₁

/-- Given a universe polymorphic functor `M.{u}`, this class helps move from
`M.{u}` to `M.{v}` and back -/
class liftable (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) :=
(up {}   : Π {α β}, α ≃ β → f α → g β)
(down {} : Π {α β}, α ≃ β → g β → f α)
(up_down : ∀ {α β} (F : α ≃ β) (x : g β), up F (down F x) = x)
(down_up : ∀ {α β} (F : α ≃ β) (x : f α), down F (up F x) = x)

attribute [simp] liftable.up_down liftable.down_up

namespace liftable

/-- The most common practical use, this function takes `x : M.{u} α` and lift it
to M.{max u v} (ulift.{v} α) -/
@[reducible]
def up' {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} : f α → g (ulift α) :=
liftable.up equiv.ulift.symm

/-- The most common practical use, this function takes `x : M.{max u v} (ulift.{v} α)`
and lowers it to `M.{u} α` -/
@[reducible]
def down' {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} : g (ulift α) → f α :=
liftable.down equiv.ulift.symm

end liftable

open ulift

protected lemma prod.map_map {α α' α'' β β' β''}
  (x : α × β) (f : α → α') (f' : α' → α'')
              (g : β → β') (g' : β' → β'') :
  prod.map f' g' (prod.map f g x) = prod.map (f' ∘ f) (g' ∘ g) x :=
by cases x; refl

protected lemma prod.id_map {α β}
  (x : α × β) :
  prod.map (λ x, x) (λ x, x) x = x :=
by cases x; refl

instance : liftable id id :=
{ up := λ _ _ F, F
, down := λ _ _ F, F.symm
, up_down := by intros; simp
, down_up := by intros; simp }

/-- for specific state types, this function helps to create a liftable instance -/
def state_t.liftable' {s s' m m'}
  [liftable m m']
  (F : s ≃ s') :
  liftable (state_t s m) (state_t s' m') :=
{ up   := λ _ _ G ⟨ f ⟩, ⟨ λ s, liftable.up (equiv.prod_congr G F) (f $ F.symm s) ⟩
, down := λ _ _ G ⟨ g ⟩, ⟨ λ s, liftable.down (equiv.prod_congr G F) $ g (F s) ⟩
, up_down := by { rintros α β G ⟨ f ⟩, simp! }
, down_up := by { rintros α β G ⟨ g ⟩, simp! [map_map,function.comp] } }

instance {s m m'}
  [liftable m m'] :
  liftable (state_t s m) (state_t (ulift s) m') :=
state_t.liftable' equiv.ulift.symm

/-- for specific reader monads, this function helps to create a liftable instance -/
def reader_t.liftable' {s s' m m'}
  [liftable m m']
  (F : s ≃ s') :
  liftable (reader_t s m) (reader_t s' m') :=
{ up   := λ _ _ G ⟨ f ⟩, ⟨ λ s, liftable.up G (f $ F.symm s) ⟩
, down := λ _ _ G ⟨ g ⟩, ⟨ λ s, liftable.down G $ g $ F s ⟩
, up_down := by { rintros α β G ⟨ f ⟩, simp! }
, down_up := by { rintros α β G ⟨ g ⟩, simp! [map_map,function.comp] } }

instance {s m m'} [liftable m m'] : liftable (reader_t s m) (reader_t (ulift s) m') :=
reader_t.liftable' equiv.ulift.symm
