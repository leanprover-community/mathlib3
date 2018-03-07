/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Standard identity and composition functors
-/
import tactic.ext
import category.basic

universe variables u v w u' v' w'

section functor

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F] [is_lawful_functor F]

lemma functor.map_id : functor.map id = (id : F α → F α) :=
by apply funext; apply id_map

lemma functor.map_comp_map (f : α → β) (g : β → γ) :
  (functor.map g ∘ functor.map f : F α → F γ) = functor.map (g ∘ f) :=
by apply funext; intro; rw comp_map

@[norm]
lemma functor.map_map (f : α → β) (g : β → γ) (x : F α) :
  g <$> f <$> x = (g ∘ f) <$> x :=
by rw ← comp_map

end functor

def id.mk {α : Sort u} : α → id α := id

namespace functor

structure comp (f : Type u → Type u') (g : Type v → Type u) (α : Type v) : Type u' :=
(run : f $ g α)

@[extensionality]
lemma comp.ext {f : Type u → Type u'} {g : Type v → Type u} {α : Type v}
  {x y : comp f g α}
  (h : x.run = y.run) :
  x = y := by cases x; cases y; cases h; refl

instance : functor id :=
{ map := λ α β f, f }
instance : is_lawful_functor id :=
{ id_map := λ α x, rfl,
  comp_map := λ α β γ f g x, rfl }

namespace comp

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [functor f] [functor g]

protected def map {α β : Type v} (h : α → β) : comp f g α → comp f g β
| ⟨x⟩ := ⟨functor.map h <$> x⟩

variables [is_lawful_functor f] [is_lawful_functor g]
variables {α β γ : Type v}

local infix ` <$> ` := comp.map

lemma id_map : ∀ (x : comp f g α), comp.map id x = x
| ⟨x⟩ :=
by simp [comp.map,functor.map_id]

protected lemma comp_map (g_1 : α → β) (h : β → γ) : ∀ (x : comp f g α),
           comp.map (h ∘ g_1) x = comp.map h (comp.map g_1 x)
| ⟨x⟩ :=
by simp [comp.map,functor.map_comp_map g_1 h] with norm

instance {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g] :
  functor (comp f g) :=
{ map := @comp.map f g _ _ }

instance {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g]
  [is_lawful_functor f] [is_lawful_functor g] :
  is_lawful_functor (comp f g) :=
{ id_map := @comp.id_map f g _ _ _ _,
  comp_map := @comp.comp_map f g _ _ _ _ }

end comp

@[norm]
lemma comp.map_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α)) :
  h <$> comp.mk x = comp.mk (functor.map h <$> x) := rfl

end functor

namespace ulift

instance : functor ulift :=
{ map := λ α β f, up ∘ f ∘ down }

end ulift

namespace sum

variables {γ α β : Type v}

protected def mapr (f : α → β) : γ ⊕ α → γ ⊕ β
| (inl x) := inl x
| (inr x) := inr (f x)

instance : functor (sum γ) :=
{ map := @sum.mapr γ }

instance : is_lawful_functor.{v} (sum γ) :=
{ id_map := by intros; casesm _ ⊕ _; refl,
  comp_map := by intros; casesm _ ⊕ _; refl }

end sum
