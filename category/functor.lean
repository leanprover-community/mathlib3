/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Standard identity and composition functors
-/
import tactic.ext
import category.basic

universe variables u v w

section functor

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F] [is_lawful_functor F]

lemma functor.map_id : (<$>) id = (id : F α → F α) :=
by apply funext; apply id_map

lemma functor.map_comp_map (f : α → β) (g : β → γ) :
  ((<$>) g ∘ (<$>) f : F α → F γ) = (<$>) (g ∘ f) :=
by apply funext; intro; rw comp_map

end functor

def id.mk {α : Sort u} : α → id α := id

namespace functor

/-- `functor.comp` is a wrapper around `function.comp` for types.
    It prevents Lean's type class resolution mechanism from trying
    a `functor (comp f id)` when `functor f` would do. -/
structure comp (f : Type u → Type w) (g : Type v → Type u) (α : Type v) : Type w :=
(run : f $ g α)

@[extensionality]
protected lemma comp.ext {f : Type u → Type w} {g : Type v → Type u} {α : Type v} :
  ∀ {x y : comp f g α}, x.run = y.run → x = y
| ⟨x⟩ ⟨._⟩ rfl := rfl

namespace comp

variables {f : Type u → Type w} {g : Type v → Type u}

variables [functor f] [functor g]

protected def map {α β : Type v} (h : α → β) : comp f g α → comp f g β
| ⟨x⟩ := ⟨(<$>) h <$> x⟩

variables [is_lawful_functor f] [is_lawful_functor g]
variables {α β γ : Type v}

protected lemma id_map : ∀ (x : comp f g α), comp.map id x = x
| ⟨x⟩ :=
by simp [comp.map,functor.map_id]

protected lemma comp_map (g_1 : α → β) (h : β → γ) : ∀ (x : comp f g α),
           comp.map (h ∘ g_1) x = comp.map h (comp.map g_1 x)
| ⟨x⟩ :=
by simp [comp.map,functor.map_comp_map g_1 h] with functor_norm

instance {f : Type u → Type w} {g : Type v → Type u}
  [functor f] [functor g] :
  functor (comp f g) :=
{ map := @comp.map f g _ _ }

@[simp]
protected lemma run_map {α β : Type v} (h : α → β) :
  ∀ x : comp f g α, (h <$> x).run = (<$>) h <$> x.run
| ⟨_⟩ := rfl

instance {f : Type u → Type w} {g : Type v → Type u}
  [functor f] [functor g]
  [is_lawful_functor f] [is_lawful_functor g] :
  is_lawful_functor (comp f g) :=
{ id_map := @comp.id_map f g _ _ _ _,
  comp_map := @comp.comp_map f g _ _ _ _ }

end comp

@[functor_norm]
lemma comp.map_mk {α β : Type w}
  {f : Type u → Type v} {g : Type w → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α)) :
  h <$> comp.mk x = comp.mk ((<$>) h <$> x) := rfl

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
