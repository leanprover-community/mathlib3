
import data.equiv.basic
import tactic

universes u₀ v₀ u₁ v₁ v₂ w w₀ w₁

class liftable (α : Type u₀) (β : (Type v₀)) :=
  (lift {}   : α ≃ β)

-- instance {α} : liftable α (ulift α) :=
-- ⟨ equiv.ulift.symm ⟩

instance ulift.liftable.ulift {α : Type w} : liftable (ulift.{u₀} α) (ulift.{u₁} α) :=
⟨ equiv.trans equiv.ulift equiv.ulift.symm ⟩

class liftable1 (f : (Type u₀ → Type u₁)) (g : Type v₀ → Type v₁) :=
  (up   : Π {α β}, α ≃ β → f α → g β)
  (down : Π {α β}, α ≃ β → g β → f α)
  (up_down : ∀ {α β} (F : α ≃ β) (x : g β), up F (down F x) = x)
  (down_up : ∀ {α β} (F : α ≃ β) (x : f α), down F (up F x) = x)

attribute [simp] liftable1.up_down liftable1.down_up

namespace liftable

@[reducible]
def up' {f : Type v₀ → Type v₁} (g : Type (max u₀ v₀) → Type u₁) [liftable1 f g]
  {α} : f α → g (ulift.{u₀} α) :=
liftable1.up g equiv.ulift.symm

@[reducible]
def down' {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [liftable1 f g]
  {α} : g (ulift α) → f α :=
liftable1.down _ equiv.ulift.symm

@[reducible]
def shift' {f : Type (max w u₀) → Type u₁} {g : Type (max w v₀) → Type v₁} [liftable1 f g]
  {α : Type w} : g (ulift α) → f (ulift α) :=
liftable1.down _ $ equiv.trans equiv.ulift equiv.ulift.symm

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

instance : liftable1 id id :=
{ up := λ _ _ F, F
, down := λ _ _ F, F.symm
, up_down := by intros; simp
, down_up := by intros; simp }

def state_t.liftable' {s : Type u₀} {s' : Type u₁} {m m'} [functor m'] [functor m] [is_lawful_functor m'] [is_lawful_functor m]
  [liftable1 m m']
  (F : s ≃ s') :
  liftable1 (state_t s m) (state_t s' m') :=
{ up   := λ _ _ G ⟨ f ⟩, ⟨ λ s, liftable1.up _ (equiv.prod_congr G F) (f $ F.symm s) ⟩
, down := λ _ _ G ⟨ g ⟩, ⟨ λ s, liftable1.down _ (equiv.prod_congr G F) $ g (F s) ⟩
, up_down := by { rintros α β G ⟨ f ⟩, simp! }
, down_up := by { rintros α β G ⟨ g ⟩, simp! [map_map,function.comp] } }

instance {s : Type u₀} {s' : Type u₁} {m m'} [functor m'] [functor m] [is_lawful_functor m'] [is_lawful_functor m]
  [liftable1 m m'] [liftable s s'] :
  liftable1 (state_t s m) (state_t s' m') :=
state_t.liftable' liftable.lift

def reader_t.liftable' {s : Type u₀} {s' : Type u₁} {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁}
  [liftable1 m m']
  (F : s ≃ s') :
  liftable1 (reader_t s m) (reader_t s' m') :=
{ up   := λ _ _ G ⟨ f ⟩, ⟨ λ s, liftable1.up _ G (f $ F.symm s) ⟩
, down := λ _ _ G ⟨ g ⟩, ⟨ λ s, liftable1.down _ G $ g $ F s ⟩
, up_down := by { rintros α β G ⟨ f ⟩, simp! }
, down_up := by { rintros α β G ⟨ g ⟩, simp! [map_map,function.comp] } }

instance {s : Type u₀} {s' : Type u₁} {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁}
  [liftable1 m m'] [liftable s s'] :
  liftable1 (reader_t s m) (reader_t s' m') :=
reader_t.liftable' liftable.lift

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

instance : liftable1 option.{u₀} option.{v₁} :=
{ up := λ α β eq, @option.rec _ (λ _, option β) (@none β) (λ x, some $ eq x)
, down := λ α β eq, @option.rec _ (λ _, option α) (@none α) (λ x, some $ eq.symm x)
, up_down := by intros; cases x; simp
, down_up := by intros; cases x; simp }

namespace pliftable

@[reducible]
def up' {f : Type v₀ → Type v₁} (g : Type u₀ → Type u₁) [liftable1 f g] :
  f punit → g punit :=
liftable1.up g equiv.punit_equiv_punit

@[reducible]
def down' {f : Type u₀ → Type u₁} {g : Type v₀ → Type v₁} [liftable1 f g] :
  g punit → f punit :=
liftable1.down _ equiv.punit_equiv_punit

end pliftable
