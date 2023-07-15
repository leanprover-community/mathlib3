/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import topology.sheaves.sheaf_condition.sites

/-!
# Presheaves on punit

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Presheaves on punit satisfy sheaf condition iff its value at empty set is a terminal object.
-/

namespace Top.presheaf

universes u v w

open category_theory category_theory.limits Top opposite

variables {C : Type u} [category.{v} C]

lemma is_sheaf_of_is_terminal_of_indiscrete {X : Top.{w}} (hind : X.str = ⊤) (F : presheaf C X)
  (it : is_terminal $ F.obj $ op ⊥) : F.is_sheaf :=
λ c U s hs, begin
  obtain rfl | hne := eq_or_ne U ⊥,
  { intros _ _, rw @exists_unique_iff_exists _ ⟨λ _ _, _⟩,
    { refine ⟨it.from _, λ U hU hs, is_terminal.hom_ext _ _ _⟩, rwa le_bot_iff.1 hU.le },
    { apply it.hom_ext } },
  { convert presieve.is_sheaf_for_top_sieve _, rw ←sieve.id_mem_iff_eq_top,
    have := (U.eq_bot_or_top hind).resolve_left hne, subst this,
    obtain he | ⟨⟨x⟩⟩ := is_empty_or_nonempty X,
    { exact (hne $ set_like.ext'_iff.2 $ set.univ_eq_empty_iff.2 he).elim },
    obtain ⟨U, f, hf, hm⟩ := hs x trivial,
    obtain rfl | rfl := U.eq_bot_or_top hind,
    { cases hm }, { convert hf } },
end

lemma is_sheaf_iff_is_terminal_of_indiscrete {X : Top.{w}} (hind : X.str = ⊤)
  (F : presheaf C X) : F.is_sheaf ↔ nonempty (is_terminal $ F.obj $ op ⊥) :=
⟨λ h, ⟨sheaf.is_terminal_of_empty ⟨F, h⟩⟩, λ ⟨it⟩, is_sheaf_of_is_terminal_of_indiscrete hind F it⟩

lemma is_sheaf_on_punit_of_is_terminal (F : presheaf C (Top.of punit))
  (it : is_terminal $ F.obj $ op ⊥) : F.is_sheaf :=
is_sheaf_of_is_terminal_of_indiscrete (@subsingleton.elim (topological_space punit) _ _ _) F it

lemma is_sheaf_on_punit_iff_is_terminal (F : presheaf C (Top.of punit)) :
  F.is_sheaf ↔ nonempty (is_terminal $ F.obj $ op ⊥) :=
⟨λ h, ⟨sheaf.is_terminal_of_empty ⟨F, h⟩⟩, λ ⟨it⟩, is_sheaf_on_punit_of_is_terminal F it⟩

end Top.presheaf
