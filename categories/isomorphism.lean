-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism
universes u

variable {C : Type u}
variable [category C]
variables {X Y Z : C}

structure Isomorphism (X Y : C) :=
(morphism : Hom X Y)
(inverse : Hom Y X)
(witness_1 : morphism >> inverse = 𝟙 X . obviously)
(witness_2 : inverse >> morphism = 𝟙 Y . obviously)

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

instance Isomorphism_coercion_to_morphism : has_coe (Isomorphism X Y) (Hom X Y) :=
  {coe := Isomorphism.morphism}

definition IsomorphismComposition (α : Isomorphism X Y) (β : Isomorphism Y Z) : Isomorphism X Z :=
{
  morphism := α.morphism >> β.morphism,
  inverse := β.inverse >> α.inverse
}

@[applicable] lemma Isomorphism_pointwise_equal
  (α β : Isomorphism X Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        -- PROJECT why can't we automate this?
        tidy,
        resetI,
        rewrite ← @category.left_identity C _ _ _ k,
        rewrite ← wα2,
        rewrite category.associativity,
        simp *,
      end,
    smt_eblast
  end

definition Isomorphism.reverse (I : Isomorphism X Y) : Isomorphism Y X := {
  morphism  := I.inverse,
  inverse   := I.morphism
}

structure is_Isomorphism (morphism : Hom X Y) :=
(inverse : Hom Y X)
(witness_1 : morphism >> inverse = 𝟙 X . obviously)
(witness_2 : inverse >> morphism = 𝟙 Y . obviously)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism (f : Hom X Y): has_coe (is_Isomorphism f) (Hom X Y) :=
  {coe := λ _, f}

definition Epimorphism (f : Hom X Y) := Π (g h : Hom Y Z) (w : f >> g = f >> h), g = h
definition Monomorphism (f : Hom X Y) := Π (g h : Hom Z X) (w : g >> f = h >> f), g = h

end categories.isomorphism
