/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import control.bitraversable.lemmas
import control.traversable.lemmas

/-!
# bitraversable instances

## Instances

 * prod
 * sum
 * const
 * flip
 * bicompl
 * bicompr

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative

-/

universes u v w

variables {t : Type u → Type u → Type u} [bitraversable t]

section
variables {F : Type u → Type u} [applicative F]

def prod.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : α × β → F (α' × β')
| (x,y) := prod.mk <$> f x <*> f' y

instance : bitraversable prod :=
{ bitraverse := @prod.bitraverse }

instance : is_lawful_bitraversable prod :=
by constructor; introsI; cases x;
     simp [bitraverse,prod.bitraverse] with functor_norm; refl

open functor

def sum.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : α ⊕ β → F (α' ⊕ β')
| (sum.inl x) := sum.inl <$> f x
| (sum.inr x) := sum.inr <$> f' x

instance : bitraversable sum :=
{ bitraverse := @sum.bitraverse }

instance : is_lawful_bitraversable sum :=
by constructor; introsI; cases x;
     simp [bitraverse,sum.bitraverse] with functor_norm; refl

def const.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : const α β → F (const α' β') := f

instance bitraversable.const : bitraversable const :=
{ bitraverse := @const.bitraverse }

instance is_lawful_bitraversable.const : is_lawful_bitraversable const  :=
by constructor; introsI;
     simp [bitraverse,const.bitraverse] with functor_norm; refl

def flip.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : flip t α β → F (flip t α' β') :=
(bitraverse f' f : t β α → F (t β' α'))

instance bitraversable.flip : bitraversable (flip t) :=
{ bitraverse := @flip.bitraverse t _ }

open is_lawful_bitraversable
instance is_lawful_bitraversable.flip [is_lawful_bitraversable t]
  : is_lawful_bitraversable (flip t)  :=
by constructor; intros; unfreezingI { casesm is_lawful_bitraversable t }; tactic.apply_assumption

open bitraversable functor

@[priority 10]
instance bitraversable.traversable {α} : traversable (t α) :=
{ traverse := @tsnd t _ _ }

@[priority 10]
instance bitraversable.is_lawful_traversable [is_lawful_bitraversable t] {α} :
  is_lawful_traversable (t α) :=
by { constructor; introsI; simp [traverse,comp_tsnd] with functor_norm,
     { refl },
     { simp [tsnd_eq_snd_id], refl },
     { simp [tsnd,binaturality,function.comp] with functor_norm } }

end

open bifunctor traversable is_lawful_traversable is_lawful_bitraversable
open function (bicompl bicompr)

section bicompl
variables (F G : Type u → Type u) [traversable F] [traversable G]

def bicompl.bitraverse {m} [applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
  bicompl t F G α α' → m (bicompl t F G β β') :=
(bitraverse (traverse f) (traverse f') : t (F α) (G α') → m _)

instance : bitraversable (bicompl t F G) :=
{ bitraverse := @bicompl.bitraverse t _ F G _ _ }

instance [is_lawful_traversable F]  [is_lawful_traversable G] [is_lawful_bitraversable t] :
  is_lawful_bitraversable (bicompl t F G) :=
begin
  constructor; introsI;
    simp [bitraverse, bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse]
      with functor_norm,
  { simp [traverse_eq_map_id',bitraverse_eq_bimap_id], },
  { revert x, dunfold bicompl,
    simp [binaturality,naturality_pf] }
end

end bicompl
section bicompr

variables (F : Type u → Type u) [traversable F]

def bicompr.bitraverse {m} [applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
  bicompr F t α α' → m (bicompr F t β β') :=
(traverse (bitraverse f f') : F (t α α') → m _)

instance : bitraversable (bicompr F t) :=
{ bitraverse := @bicompr.bitraverse t _ F _ }

instance [is_lawful_traversable F] [is_lawful_bitraversable t] :
  is_lawful_bitraversable (bicompr F t) :=
begin
  constructor; introsI;
    simp [bitraverse,bicompr.bitraverse,bitraverse_id_id] with functor_norm,
  { simp [bitraverse_eq_bimap_id',traverse_eq_map_id'], refl },
  { revert x, dunfold bicompr, intro,
    simp [naturality,binaturality'] }
end

end bicompr
