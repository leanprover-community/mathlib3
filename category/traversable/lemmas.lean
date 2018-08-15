/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Lemmas about traversing collections.

Inspired by:

    The Essence of the Iterator Pattern
    Jeremy Gibbons and Bruno César dos Santos Oliveira
    In Journal of Functional Programming. Vol. 19. No. 3&4. Pages 377−402. 2009.
    http://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf
-/

import tactic.cache
import category.traversable.basic

universe variables u

open is_lawful_traversable
open function (hiding comp)
open functor

attribute [functor_norm] is_lawful_traversable.naturality

namespace traversable

variable {t : Type u → Type u}
variables [traversable t] [is_lawful_traversable t]
variables {G H : Type u → Type u}

variables [applicative G] [is_lawful_applicative G]
variables [applicative H] [is_lawful_applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ

variables G H

def pure_transformation : applicative_transformation id G :=
begin
  refine { F := @pure G _, .. }; intros,
  { refl },
  { simp, refl }
end

variables {G H}

lemma traverse_eq_map_ident (x : t β) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
calc
      traverse (id.mk ∘ f) x
    = traverse id.mk (f <$> x) : by rw [← traverse_map]
... = (<$>) f <$> x            : by simp [id_traverse]; refl

lemma purity (x : t α) :
  traverse pure x = (pure x : G (t α)) :=
let η := pure_transformation G in
calc   traverse (@pure G _ _) x
     = traverse (pure ∘ id.mk) x : rfl
 ... = traverse (@η _ ∘ id.mk) x : rfl
 ... = η (traverse id.mk x)      : by rw [naturality]
 ... = η x                       : by rw [id_traverse]
 ... = pure x                    : rfl

lemma id_sequence (x : t α) :
  sequence (id.mk <$> x) = id.mk x :=
by simp [sequence,traverse_map,id_traverse]; refl

lemma comp_sequence (x : t (G (H α))) :
  sequence (comp.mk <$> x) = comp.mk (sequence <$> sequence x) :=
by simp [sequence,traverse_map]; rw ← comp_traverse; simp [map_id]

lemma naturality' (η : applicative_transformation G H) (x : t (G α)) :
  η (sequence x) = sequence (@η _ <$> x) :=
by simp [sequence,naturality,traverse_map]

end traversable
