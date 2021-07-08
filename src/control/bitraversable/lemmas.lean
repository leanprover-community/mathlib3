/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.bitraversable.basic

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/

universes u

variables {t : Type u → Type u → Type u} [bitraversable t]
variables {β : Type u}

namespace bitraversable
open functor is_lawful_applicative
variables {F G : Type u → Type u}
          [applicative F] [applicative G]

/-- traverse on the first functor argument -/
@[reducible] def tfst {α α'} (f : α → F α') : t α β → F (t α' β) :=
bitraverse f pure

/-- traverse on the second functor argument -/
@[reducible] def tsnd {α α'} (f : α → F α') : t β α → F (t β α') :=
bitraverse pure f

variables [is_lawful_bitraversable t]
          [is_lawful_applicative F]
          [is_lawful_applicative G]

@[higher_order tfst_id]
lemma id_tfst : Π {α β} (x : t α β), tfst id.mk x = id.mk x :=
@id_bitraverse _ _ _

@[higher_order tsnd_id]
lemma id_tsnd : Π {α β} (x : t α β), tsnd id.mk x = id.mk x :=
@id_bitraverse _ _ _

@[higher_order tfst_comp_tfst]
lemma comp_tfst {α₀ α₁ α₂ β}
  (f : α₀ → F α₁) (f' : α₁ → G α₂) (x : t α₀ β) :
  comp.mk (tfst f' <$> tfst f x) = tfst (comp.mk ∘ map f' ∘ f) x :=
by rw ← comp_bitraverse; simp [tfst,map_comp_pure,has_pure.pure]

@[higher_order tfst_comp_tsnd]
lemma tfst_tsnd {α₀ α₁ β₀ β₁}
  (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
  comp.mk (tfst f <$> tsnd f' x) =
  bitraverse (comp.mk ∘ pure ∘ f) (comp.mk ∘ map pure ∘ f') x :=
by rw ← comp_bitraverse; simp [tfst,tsnd]

@[higher_order tsnd_comp_tfst]
lemma tsnd_tfst {α₀ α₁ β₀ β₁}
  (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
  comp.mk (tsnd f' <$> tfst f x) =
  bitraverse (comp.mk ∘ map pure ∘ f) (comp.mk ∘ pure ∘ f') x :=
by rw ← comp_bitraverse; simp [tfst,tsnd]

@[higher_order tsnd_comp_tsnd]
lemma comp_tsnd {α β₀ β₁ β₂}
  (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) :
  comp.mk (tsnd g' <$> tsnd g x) = tsnd (comp.mk ∘ map g' ∘ g) x :=
by rw ← comp_bitraverse; simp [tsnd]; refl

open bifunctor

private lemma pure_eq_id_mk_comp_id {α} :
  pure = id.mk ∘ @id α := rfl

open function

@[higher_order]
lemma tfst_eq_fst_id {α α' β} (f : α → α') (x : t α β) :
  tfst (id.mk ∘ f) x = id.mk (fst f x) :=
by simp [tfst,fst,pure_eq_id_mk_comp_id,-comp.right_id,bitraverse_eq_bimap_id]

@[higher_order]
lemma tsnd_eq_snd_id {α β β'} (f : β → β') (x : t α β) :
  tsnd (id.mk ∘ f) x = id.mk (snd f x) :=
by simp [tsnd,snd,pure_eq_id_mk_comp_id,-comp.right_id,bitraverse_eq_bimap_id]

attribute [functor_norm] comp_bitraverse comp_tsnd comp_tfst
  tsnd_comp_tsnd tsnd_comp_tfst tfst_comp_tsnd tfst_comp_tfst
  bitraverse_comp bitraverse_id_id tfst_id tsnd_id

end bitraversable
