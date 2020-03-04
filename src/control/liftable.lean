
import data.equiv.basic
import tactic

universes u₀ u₁ v₀ v₁ v₂ w w₀ w₁

class liftable (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) :=
  (up {}   : Π {α β}, α ≃ β → f α → g β)
  (down {} : Π {α β}, α ≃ β → g β → f α)
  (up_down : ∀ {α β} (F : α ≃ β) (x : g β), up F (down F x) = x)
  (down_up : ∀ {α β} (F : α ≃ β) (x : f α), down F (up F x) = x)

attribute [simp] liftable.up_down liftable.down_up

namespace liftable

@[reducible]
def up' {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable f g]
  {α} : f α → g (ulift α) :=
liftable.up equiv.ulift.symm

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

def state_t.liftable' {s s' m m'} [functor m'] [functor m] [is_lawful_functor m'] [is_lawful_functor m]
  [liftable m m']
  (F : s ≃ s') :
  liftable (state_t s m) (state_t s' m') :=
{ up   := λ _ _ G ⟨ f ⟩, ⟨ λ s, liftable.up (equiv.prod_congr G F) (f $ F.symm s) ⟩
, down := λ _ _ G ⟨ g ⟩, ⟨ λ s, liftable.down (equiv.prod_congr G F) $ g (F s) ⟩
, up_down := by { rintros α β G ⟨ f ⟩, simp! }
, down_up := by { rintros α β G ⟨ g ⟩, simp! [map_map,function.comp] } }

instance {s m m'} [functor m'] [functor m] [is_lawful_functor m'] [is_lawful_functor m]
  [liftable m m'] :
  liftable (state_t s m) (state_t (ulift s) m') :=
state_t.liftable' equiv.ulift.symm

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

-- namespace liftable

-- variables {f : Type (max u₀ w) → Type u₁} {g : Type (max (max u₀ w) v₀) → Type v₁}
-- variables [liftable f g] [functor g]
-- variable {α : Type w}
-- open functor

-- def up' (x : f (ulift.{u₀} α)) : g (ulift.{max u₀ v₀} α) :=
-- map (ulift.up ∘ ulift.down ∘ ulift.down) $ up x

-- def down' (x : g (ulift.{max u₀ v₀} α)) : f (ulift.{u₀} α) :=
-- down $ map (ulift.up ∘ ulift.up ∘ ulift.down) x

-- variables [is_lawful_functor g]

-- lemma up_down' : ∀ (x : g (ulift.{max u₀ v₀} α)), up' (down' x : f (ulift.{u₀} α)) = x :=
-- by intros; simp [up',down',map_map,function.comp,ulift.up_down]

-- lemma down_up' : ∀ (x : f (ulift.{u₀} α)), down' (up' x : g (ulift.{max u₀ v₀} α)) = x :=
-- by intros; simp [up',down',map_map,function.comp,ulift.up_down]

-- end liftable

section trans
open liftable

-- def liftable.trans
--     {f : Type u₀ → Type u₁}
--     {g : Type v₀ → Type v₁}
--     {h : Type w₀ → Type w₁}
--     [functor h] [is_lawful_functor h]
--     (_ : liftable f g)
--     (_ : liftable g h) :
--   liftable f h :=
-- by refine
--      { up := λ α β G, (up' : g (ulift α) → h (ulift.{max v₀ w} α)) ∘ (up : f α → g (ulift α)),
--        down := λ α β G, (down : g (ulift α) → f α) ∘ (down' : h (ulift.{max v₀ w} α) → g (ulift α)) ,
--        .. };
--      intros; simp [function.comp,up_down',down_up']

end trans
