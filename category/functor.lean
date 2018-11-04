/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Standard identity and composition functors
-/
import tactic.ext tactic.cache category.basic

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

theorem functor.ext {F} : ∀ {F1 : functor F} {F2 : functor F}
  [@is_lawful_functor F F1] [@is_lawful_functor F F2]
  (H : ∀ α β (f : α → β) (x : F α),
    @functor.map _ F1 _ _ f x = @functor.map _ F2 _ _ f x),
  F1 = F2
| ⟨m, mc⟩ ⟨m', mc'⟩ H1 H2 H :=
begin
  cases show @m = @m', by funext α β f x; apply H,
  congr, funext α β,
  have E1 := @map_const_eq _ ⟨@m, @mc⟩ H1,
  have E2 := @map_const_eq _ ⟨@m, @mc'⟩ H2,
  exact E1.trans E2.symm
end

end functor

def id.mk {α : Sort u} : α → id α := id

namespace functor

/-- `functor.comp` is a wrapper around `function.comp` for types.
    It prevents Lean's type class resolution mechanism from trying
    a `functor (comp F id)` when `functor F` would do. -/
def comp (F : Type u → Type w) (G : Type v → Type u) (α : Type v) : Type w :=
F $ G α

@[pattern] def comp.mk {F : Type u → Type w} {G : Type v → Type u} {α : Type v}
  (x : F (G α)) : comp F G α := x

def comp.run {F : Type u → Type w} {G : Type v → Type u} {α : Type v}
  (x : comp F G α) : F (G α) := x

namespace comp

variables {F : Type u → Type w} {G : Type v → Type u}

protected lemma ext
  {α} {x y : comp F G α} : x.run = y.run → x = y := id

variables [functor F] [functor G]

protected def map {α β : Type v} (h : α → β) : comp F G α → comp F G β
| (comp.mk x) := comp.mk ((<$>) h <$> x)

instance : functor (comp F G) := { map := @comp.map F G _ _ }

@[functor_norm] lemma map_mk {α β} (h : α → β) (x : F (G α)) :
  h <$> comp.mk x = comp.mk ((<$>) h <$> x) := rfl

variables [is_lawful_functor F] [is_lawful_functor G]
variables {α β γ : Type v}

protected lemma id_map : ∀ (x : comp F G α), comp.map id x = x
| (comp.mk x) := by simp [comp.map, functor.map_id]

protected lemma comp_map (g' : α → β) (h : β → γ) : ∀ (x : comp F G α),
           comp.map (h ∘ g') x = comp.map h (comp.map g' x)
| (comp.mk x) := by simp [comp.map, functor.map_comp_map g' h] with functor_norm

@[simp] protected lemma run_map (h : α → β) (x : comp F G α) :
  (h <$> x).run = (<$>) h <$> x.run := rfl

instance : is_lawful_functor (comp F G) :=
{ id_map := @comp.id_map F G _ _ _ _,
  comp_map := @comp.comp_map F G _ _ _ _ }

theorem functor_comp_id {F} [AF : functor F] [is_lawful_functor F] :
  @comp.functor F id _ _ = AF :=
@functor.ext F _ AF (@comp.is_lawful_functor F id _ _ _ _) _ (λ α β f x, rfl)

theorem functor_id_comp {F} [AF : functor F] [is_lawful_functor F] :
  @comp.functor id F _ _ = AF :=
@functor.ext F _ AF (@comp.is_lawful_functor id F _ _ _ _) _ (λ α β f x, rfl)

end comp

end functor

namespace ulift

instance : functor ulift :=
{ map := λ α β f, up ∘ f ∘ down }

end ulift
