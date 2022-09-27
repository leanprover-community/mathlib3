import topology.sheaves.sheaf

namespace category_theory

open Top category_theory.limits opposite

universes u v w

variables {C : Type u} [category.{v} C]

lemma presheaf_on_unit_is_sheaf_of_is_terminal (F : presheaf C (Top.of (punit : Type w)))
  [is_terminal $ F.obj $ op ⊥] : F.is_sheaf :=
_

lemma presheaf_on_punit_is_sheaf_iff_is_terminal (F : presheaf C (Top.of (punit : Type w))) :
  F.is_sheaf ↔ nonempty (is_terminal (F.obj (op ⊥))) :=
_

end category_theory
