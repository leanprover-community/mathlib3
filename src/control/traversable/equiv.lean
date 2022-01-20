/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.traversable.lemmas
import data.equiv.basic

/-!
# Transferring `traversable` instances along isomorphisms

This file allows to transfer `traversable` instances along isomorphisms.

## Main declarations

* `equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.functor`: `equiv.map` as a functor.
* `equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.traversable`: `equiv.traverse` as a traversable functor.
* `equiv.is_lawful_traversable`: `equiv.traverse` as a lawful traversable functor.
-/

universes u

namespace equiv

section functor
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [functor t]

open functor

/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`equiv.functor`). -/
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
eqv β $ map f ((eqv α).symm x)

/-- The function `equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.  -/
protected def functor : functor t' :=
{ map := @equiv.map _ }

variables [is_lawful_functor t]

protected lemma id_map {α : Type u} (x : t' α) : equiv.map id x = x :=
by simp [equiv.map, id_map]

protected lemma comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
  equiv.map (h ∘ g) x = equiv.map h (equiv.map g x) :=
by simp [equiv.map]; apply comp_map

protected lemma is_lawful_functor : @is_lawful_functor _ equiv.functor :=
{ id_map := @equiv.id_map _ _,
  comp_map := @equiv.comp_map _ _ }

protected lemma is_lawful_functor' [F : _root_.functor t']
  (h₀ : ∀ {α β} (f : α → β), _root_.functor.map f = equiv.map f)
  (h₁ : ∀ {α β} (f : β), _root_.functor.map_const f = (equiv.map ∘ function.const α) f) :
  _root_.is_lawful_functor t' :=
begin
  have : F = equiv.functor,
  { casesI F, dsimp [equiv.functor],
    congr; ext; [rw ← h₀, rw ← h₁] },
  substI this,
  exact equiv.is_lawful_functor
end

end functor

section traversable
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [traversable t]
variables {m : Type u → Type u} [applicative m]
variables {α β : Type u}

/-- Like `equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α.  See `equiv.traversable`. -/
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
eqv β <$> traverse f ((eqv α).symm x)

/-- The function `equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
protected def traversable : traversable t' :=
{ to_functor := equiv.functor eqv,
  traverse := @equiv.traverse _ }

end traversable

section equiv
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [traversable t] [is_lawful_traversable t]
variables {F G : Type u → Type u} [applicative F] [applicative G]
variables [is_lawful_applicative F] [is_lawful_applicative G]
variables (η : applicative_transformation F G)
variables {α β γ : Type u}

open is_lawful_traversable functor

protected lemma id_traverse (x : t' α) :
  equiv.traverse eqv id.mk x = x :=
by simp! [equiv.traverse,id_bind,id_traverse,functor.map] with functor_norm

protected lemma traverse_eq_map_id (f : α → β) (x : t' α) :
  equiv.traverse eqv (id.mk ∘ f) x = id.mk (equiv.map eqv f x) :=
by simp [equiv.traverse, traverse_eq_map_id] with functor_norm; refl

protected lemma comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
  equiv.traverse eqv (comp.mk ∘ functor.map f ∘ g) x =
  comp.mk (equiv.traverse eqv f <$> equiv.traverse eqv g x) :=
by simp [equiv.traverse,comp_traverse] with functor_norm; congr; ext; simp

protected lemma naturality (f : α → F β) (x : t' α) :
  η (equiv.traverse eqv f x) = equiv.traverse eqv (@η _ ∘ f) x :=
by simp only [equiv.traverse] with functor_norm

/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`equiv.traversable`. -/
protected def is_lawful_traversable : @is_lawful_traversable t' (equiv.traversable eqv) :=
{ to_is_lawful_functor := @equiv.is_lawful_functor _ _ eqv _ _,
  id_traverse := @equiv.id_traverse _ _,
  comp_traverse := @equiv.comp_traverse _ _,
  traverse_eq_map_id := @equiv.traverse_eq_map_id _ _,
  naturality := @equiv.naturality _ _ }

/-- If the `traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well. -/
protected def is_lawful_traversable' [_i : traversable t']
  (h₀ : ∀ {α β} (f : α → β),
         map f = equiv.map eqv f)
  (h₁ : ∀ {α β} (f : β),
         map_const f = (equiv.map eqv ∘ function.const α) f)
  (h₂ : ∀ {F : Type u → Type u} [applicative F],
        by exactI ∀ [is_lawful_applicative F]
          {α β} (f : α → F β),
         traverse f = equiv.traverse eqv f) :
  _root_.is_lawful_traversable t' :=
begin
    -- we can't use the same approach as for `is_lawful_functor'` because
    -- h₂ needs a `is_lawful_applicative` assumption
  refine {to_is_lawful_functor :=
    equiv.is_lawful_functor' eqv @h₀ @h₁, ..}; introsI,
  { rw [h₂, equiv.id_traverse], apply_instance },
  { rw [h₂, equiv.comp_traverse f g x, h₂], congr,
    rw [h₂], all_goals { apply_instance } },
  { rw [h₂, equiv.traverse_eq_map_id, h₀]; apply_instance },
  { rw [h₂, equiv.naturality, h₂]; apply_instance }
end

end equiv
end equiv
